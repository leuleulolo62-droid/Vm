-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = box.Text:upper()
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'xq6KYSL90x1j7VI55mlLdesN'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-4jUsioGGiPp3
return Vm.run(__src, { name = 'VolleyBall Legend/VolleyBall-Legends', checksum = 427908111, interval = 2, watermark = 'Y2k-4jUsioGGiPp3', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
